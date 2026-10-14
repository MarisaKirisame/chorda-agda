{-# OPTIONS --safe #-}

open import interface

module all (funext : Funext) (VI : VarInterface) where

import core
import compatibility
import existence
import validity
import linearity
open module coreI = core funext VI
open module compatibilityI = compatibility funext VI
open module existenceI = existence funext VI
open module validityI = validity funext VI
open module linearityI = linearity funext VI

open import instantiation
