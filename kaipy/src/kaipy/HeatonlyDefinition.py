import functools as F
import typing as T

import pyk.kore.syntax as Kore


def attr_is_heating_cooling(attr: Kore.App):
    return attr.symbol in {"heat", "cool"}


def sentence_is_heating_cooling_or_other(sentence: Kore.Sentence) -> bool:
    match sentence:
        case Kore.Axiom(_, Kore.Rewrites(_, _, _), attrs):
            return any(map(attr_is_heating_cooling, attrs))
    return True


def heat_cool_only_module(module: Kore.Module) -> Kore.Module:
    return Kore.Module(
        name=module.name,
        sentences=[
            sentence
            for sentence in module.sentences
            if sentence_is_heating_cooling_or_other(sentence)
        ],
        attrs=module.attrs,
    )


def heat_cool_only_definition(definition: Kore.Definition) -> Kore.Definition:
    return Kore.Definition(
        modules=[heat_cool_only_module(module) for module in definition.modules],
        attrs=definition.attrs,
    )
