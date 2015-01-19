package c;

import c.Pointer;
import c.Types;

@:analyzer(no_simplification, no_const_propagation)
extern class Lib {
	public static function sizeof<T>(c:TypeReference<T>):Int;

	public static function dereference<T>(ptr:Pointer<T>):T;

	public static function getAddress<T>(t:T):Pointer<T>;

	public static function alloca(i:Int):Pointer<Void>;

	public static function cCode<T>(s:ConstPointer<Char>):T;

	public static function callMain():Void;

	public static function callCMacro<T>(name:ConstPointer<Char>, rest:Array<VarArg>):T;
}