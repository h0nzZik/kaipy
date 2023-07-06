import functools as F
import typing as T

import pyk.kore.syntax as Kore


def attr_is_heating(attr: Kore.App):
    return attr.symbol == "heat"


def sentence_is_heating(sentence: Kore.Sentence) -> bool:
    return any(map(attr_is_heating, sentence.attrs))


def heat_only_module(module: Kore.Module) -> Kore.Module:
    return Kore.Module(
        name=module.name,
        sentences=[
            sentence for sentence in module.sentences if sentence_is_heating(sentence)
        ],
        attrs=module.attrs,
    )


def heat_only_definition(definition: Kore.Definition) -> Kore.Definition:
    return Kore.Definition(
        modules=[heat_only_module(module) for module in definition.modules],
        attrs=definition.attrs,
    )
