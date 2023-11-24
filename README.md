# Introduction

TLA+ is a high-level language for modelling programs and systems. It was created
by renowned computer scientist [Leslie Lamport](https://lamport.org/) at the end
of the nineties.

# Why?

The language can be used as testable pseudocode, making engineers more confident
in the correctness of complicated system designs. Specifically changes to such
systems can be reasoned about in a safer way.

Additionally it can function as a high level technical specification (with the
potential to replace some diagrams).

For more in depth information see for example the paper
[How Amazon Web Services uses formal methods](https://www.amazon.science/publications/how-amazon-web-services-uses-formal-methods).

# Acknowledgements

The examples are taken from Hillel Wayne's fantastic book
`Practical TLA+ - Planning Driven Development` and follow the progression
through its chapters.

Also take a look at Leslie Lamport's
[comments](https://lamport.azurewebsites.net/tla/practical-tla.html).

# Installation

The official way of using TLA+ is with the
[TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html). I recommend
downloading the latest pre-release from
[github](https://github.com/tlaplus/tlaplus/releases).

Some of the examples use the `PT` library, written for the aforementioned book.
To installl it, download it from
https://github.com/Apress/practical-tla-plus/raw/master/PT/PT.tla to a folder
you can find again.

Open the TLA+ Toolbox and go to `File -> Preferences -> TLA+ Preferences`. Add
the folder with the PT library to `TLA+ library path locations`.

# Examples

For reference, a [TLA+ cheatsheet](./tla+-cheatsheet.md) is provided.

- [simple wire transfer](./examples/00_simple_wire_transfer/)
- [telephone](./examples/01_telephone/)
- [knapsack](./examples/02_knapsack/)
