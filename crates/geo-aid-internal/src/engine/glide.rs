//! Glide - Gradient-Led Iterative Descent Engine
//!
//! This is simply an implementation of the gradient descent
//! method. Details are described in the math doc.

use crate::engine::compiler::{Compiled, FigureFn};
use crate::engine::thread_pool::ThreadPool;
use crate::engine::QualityRecord;
use crate::script::figure::Generated;
use crate::script::math::Intermediate;
use geo_aid_math::Func;
use rand::Rng;
use std::time::{Duration, Instant};

/// Glide runtime.
pub struct Glide {
    /// Generation params
    params: Params,
    /// Figure error function
    error_fn: Func,
    /// Figure gradient function
    gradient_fn: Func,
    /// Figure function
    figure_fn: FigureFn,
    /// Current best state
    inputs: Vec<f64>,
}

/// Parameters modifying the behavior of Glide
#[derive(Clone, Copy)]
pub struct Params {
    /// How strictly the rules are applied
    pub strictness: f64,
    /// How many samples to try out in search for a global minimum.
    pub samples: usize,
    /// How many threads to use
    pub worker_count: usize,
    /// How many last quality deltas to use in mean calculation.
    pub mean_count: usize,
    /// If the arithmetic mean of the last `mean_count` deltas ever goes below
    /// this number, the generation process stops.
    pub max_mean_delta: f64,
}

impl Glide {
    /// Creates a new runtime based on parameters and Math IR
    #[must_use]
    pub fn new(params: Params, intermediate: &Intermediate) -> Self {
        let Compiled {
            context,
            errors,
            figure_fn,
            input_count,
            ..
        } = super::compiler::compile(intermediate);

        // let rule1 = rule_errors[0];
        // println!("Rule #1 {}", context.stringify(rule1));
        // for (i, g) in context.gradient(rule1).into_iter().enumerate() {
        //     println!("Over #{i}: {}", context.stringify(g));
        // }

        #[allow(clippy::cast_precision_loss)]
        let errors_len = context.constant(errors.len() as f64);
        // The higher the error, the worse the figure. Therefore, exponent should be positive.
        let mean_exponent = params.strictness;
        let total_error_power = errors.into_iter().fold(context.real_zero(), |a, b| {
            let b_strict = b.pow(&context.constant(mean_exponent));
            let b_divided = b_strict / &errors_len;
            a + &b_divided
        });
        let total_error = total_error_power.pow(&context.constant(mean_exponent.recip()));

        let mut rng = rand::thread_rng();
        let inputs = (0..input_count).map(|_| rng.gen::<f64>() * 10.0 - 5.0);

        Self {
            params,
            error_fn: context.exec(|ctx| ctx.compute([total_error.expr])),
            gradient_fn: context.exec(|ctx| ctx.compute_gradient(total_error.expr)),
            figure_fn,
            inputs: inputs.collect(),
        }
    }

    /// Performs a generation over the previously specified sample count.
    /// Executes `sample_complete` every time a sample is completed.
    /// Returns how long the whole process took.
    pub fn generate(&mut self, mut sample_complete: impl FnMut()) -> Duration {
        let start = Instant::now();
        let input_count = self.inputs.len();
        let params = self.params;
        let error_fn = self.error_fn;
        let gradient_fn = self.gradient_fn;
        let mut pool = ThreadPool::new(
            self.params.worker_count,
            move |_: Option<()>| GenerateContext {
                sample: vec![0.0; input_count],
                error_fn,
                gradient_fn,
                gradient: vec![0.0; input_count],
                previous_gradient: vec![0.0; input_count],
                candidate: vec![0.0; input_count],
                quality_record: QualityRecord::new(params.mean_count, params.max_mean_delta),
            },
            None,
            descend,
        );

        let mut rng = rand::thread_rng();

        let mut error = [0.0];
        self.error_fn.call(&self.inputs, &mut error);
        let mut current_quality = (-error[0]).exp();

        let mut samples_launched = 0;

        pool.execute(
            |ctx| {
                if samples_launched >= self.params.samples {
                    return false;
                }

                for input in &mut ctx.sample {
                    *input = rng.gen::<f64>() * 10.0 - 5.0;
                }

                samples_launched += 1;
                true
            },
            |ctx| {
                let q = ctx.quality_record.get_quality();
                if ctx.quality_record.get_quality() > current_quality {
                    self.inputs.clone_from(&ctx.sample);
                    current_quality = q;
                }

                sample_complete();
            },
        );

        start.elapsed()
    }

    #[must_use]
    pub fn get_figure(&self) -> Generated {
        (self.figure_fn)(&self.inputs)
    }

    #[must_use]
    pub fn get_total_quality(&self) -> f64 {
        let mut q = [0.0];
        self.error_fn.call(&self.inputs, &mut q);
        (-q[0]).exp()
    }
}

/// Context for task executors to work on.
struct GenerateContext {
    /// Input sample
    sample: Vec<f64>,
    /// Program computing figure error.
    error_fn: Func,
    /// Program computing gradient of the error function.
    gradient_fn: Func,
    /// The gradient of the error function.
    gradient: Vec<f64>,
    /// Previous gradient of error function.
    previous_gradient: Vec<f64>,
    /// Candidate sample.
    candidate: Vec<f64>,
    /// Last qualities of the figure
    quality_record: QualityRecord,
}

/// Initial speed (gradient coefficient)
const INITIAL_SPEED: f64 = 1.0;
/// If the dot product of last gradient and new gradient is lower than this,
/// speed decreases.
const DOT_THRESHOLD: f64 = 0.0;
/// If the speed ever goes below this value, generation stops.
const SPEED_LIMIT: f64 = 1e-6;

/// Finds the nearest local minimum based on the provided sample (and the remainder of context)
fn descend(ctx: &mut GenerateContext) {
    let mut speed = INITIAL_SPEED;
    let mut error = [0.0];
    let mut candidate_error = [0.0];
    ctx.error_fn.call(&ctx.sample, &mut error);
    ctx.gradient_fn.call(&ctx.sample, &mut ctx.gradient);
    ctx.previous_gradient.clone_from(&ctx.gradient);
    ctx.quality_record.clear();
    ctx.candidate.clone_from(&ctx.sample);

    loop {
        while speed > SPEED_LIMIT {
            for (delta, target) in ctx
                .gradient
                .iter()
                .copied()
                .map(|v| v * -speed)
                .zip(&mut ctx.candidate)
            {
                *target += delta;
            }

            ctx.error_fn.call(&ctx.candidate, &mut candidate_error);

            if candidate_error[0] < error[0] {
                // There's a possibility that we're "circling" around the minimum.
                // We can detect if this is the case by comparing the current gradient
                // to the previous one using dot product.
                if dot(&ctx.gradient, &ctx.previous_gradient) < DOT_THRESHOLD {
                    // println!("Slowing down because angle");
                    speed /= 1.5;
                }

                ctx.sample.clone_from_slice(&ctx.candidate);
                error = candidate_error;
                speed *= 1.1;
                break;
            }

            ctx.candidate.clone_from_slice(&ctx.sample);
            speed /= 1.5;
        }

        if ctx.quality_record.record((-error[0]).exp()) || speed < SPEED_LIMIT {
            // println!("Sample: {ctx.sample:?}");
            // println!("Gradient: {gradient:?}");
            // println!("Speed: {speed:?}");
            break;
        }

        ctx.previous_gradient.clone_from_slice(&ctx.gradient);
        ctx.gradient_fn.call(&ctx.sample, &mut ctx.gradient);
    }
}

/// A dot product of two vectors
fn dot(u: &[f64], v: &[f64]) -> f64 {
    u.iter()
        .copied()
        .zip(v.iter().copied())
        .map(|(u, v)| u * v)
        .sum()
}
