# Contributing to Geo-AID

First and foremost, check out our [code of conduct](CODE_OF_CONDUCT.md). It is crucial that all development is done in a nice and welcoming community.

## How is Geo-AID structured?

> **WARNING**: As of now, Geo-AID is undergoing some slight architectural changes. The below description regards the planned architecture. It's going to be valid when `apocalypse` gets merged into `v0.3`.

Geo-AID is divided into four main modules:

### The Compiler

GeoScript is a figure description language specifically designed for Geo-AID. The first module is responsible for compiling that language into a format understood by the generator. Apart from the standard submodules of compilers - the lexer and parser, Geo-AID has two very important steps before compilation:

#### **Unroll step**

Unrolling is responsible for removing most language abstractions. The only ones it leaves are bundles and point collections (see: language documentation). At this point, specific description of what is actually displayed on the figure is extracted and separated from figure definitions and rules. It also collects weighing information.

#### **Math step**

The math step is responsible for removing all remaining abstractions and performing optimizations on the processed script. At this point the script should be as simplified as possible to increase figure stability and reduce required computation. After this step, the figure can also be saved without further processing (not currently possible through CLI).

#### **Compiling**

Finally, the script is compiled into a critic program calculating the qualities of rules (how well each rule has been satisified) and a figure program calculating everything required for actually rendering the figure.

### The Generator

The generator is where the magic happens. The generation process consists of multiple cycles of the following form:

1. Adjust all adjustables
2. Evaluate adjustables' qualities

Adjustables are numbers representing certain objects of the figure (e. g. points). They are adjusted based on their previously evaluated qualities. The quality influences magnitude, the direction is random.

Evaluation is done by first executing the evaluation script and then calculating the weighed sum of rule qualities for each of the adjustables.

This process is performed by multiple workers (threads). After evaluation each worker submits their adjusted values along with the evaluation. The best one is picked and used as a base for the next generation cycle. When the overall quality meets a certain criteria, the process stops and outputs the final values for adjustables.

### The Projector

After generation, the projector is responsible for preparing the figure for drawing. Its job is to execute the figure script and figure out the positions of all figure objects on the drawing canvas.

### The Drawers

Geo-AID has support for multiple formats as its output. The drawers are responsible for actually drawing the figure to those formats using data precomputed by the projector.

## How can You contribute?

1. Battle testing

A very important part of Geo-AID development is testing it against different figures. You can for example test edge cases or write tests for problems from different olympiads/books. Test writing is extremely helpful, as well as bug reports.

2. Documentation

Geo-AID needs proper documentation for its language as one of its most important goals is to be as intuitive and easy to use as possible. Help in finding documentation issues and unclarities, along with actually writing the docs is going to be very appreciated.

3. Code contribution

Code contributions of any kind are welcome. We especially encourage bug fixes and drawer writing. Remember to always attach a description to what you've changed, why you've changed it and why that is an improvement.

When submitting a request, remember to always test if the code builds and to format the code. Also please test the correctness of your code. It can be done by running `test.py` with `python`. It runs all tests located in the `tests` catalog.

## How to write bug reports?

When submitting a bug report, always remember to include *the figure script* and *the command you ran Geo-AID with*. Attaching what OS you ran Geo-AID on might also be helpful, especially with performance issues.