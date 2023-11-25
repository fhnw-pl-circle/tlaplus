# Introduction

TLA+ is a high-level language for modelling programs and systems. It was created
by renowned computer scientist [Leslie Lamport](https://lamport.org/) at the end
of the nineties.

PlusCal is an imperative language which gets translated into TLA+. It has been
designed to make it easier to specify distributed algorithms, especially when
coming from a programming background, rather than a mathematical one. It was
created by Leslie Lamport as well.

# Why?

The languages can be used as testable pseudocode, making engineers more
confident in the correctness of complicated system designs. Specifically changes
to such systems can be reasoned about in a safer way.

Additionally it can function as a high level technical specification (with the
potential to replace some diagrams).

For more in depth information see for example the paper
[How Amazon Web Services uses formal methods](https://www.amazon.science/publications/how-amazon-web-services-uses-formal-methods).

# Acknowledgements

Built on the knowledge taken from the following sources:

- Leslie Lamport's
  [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html).
- Hillel Wayne's book
  [Practical TLA+ - Planning Driven Development](https://link.springer.com/book/10.1007/978-1-4842-3829-5).
- Leslie Lamport's
  [PlusCal Tutorial](https://lamport.azurewebsites.net/tla/tutorial/home.html).
- Leslie Lamport's book
  [Specifying Systems](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf).

The examples are taken from `Practical TLA+` and follow the progression through
its chapters.

Also take a look at Leslie Lamport's
[comments](https://lamport.azurewebsites.net/tla/practical-tla.html).

# Installation

The official way of using TLA+ is with the
[TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html). I recommend
downloading the latest pre-release from
[github](https://github.com/tlaplus/tlaplus/releases).

Some of the examples use the `PT` library, written for the `Practical TLA+`
book. To installl it, download it from
https://github.com/Apress/practical-tla-plus/raw/master/PT/PT.tla to a folder
you can find again.

Open the TLA+ Toolbox and go to `File -> Preferences -> TLA+ Preferences`. Add
the folder with the PT library to `TLA+ library path locations`.

# Examples

For reference, a [TLA+ cheatsheet](./tla+-cheatsheet.md) is provided.

- [die hard jug problem](./examples/die_hard_jugs/)
- [simple wire transfer](./examples/simple_wire_transfer/)
- [telephone](./examples/telephone/)
- [knapsack](./examples/knapsack/)
- [resources](./examples/resources/)
