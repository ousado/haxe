/*
 * Copyright (C)2005-2012 Haxe Foundation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

import c.Pointer;
import c.TypeReference;
import c.FixedArray;
import c.Lib;
import c.Types.Char;
import c.CStdio;
import c.CString;

import c.NInt.Int64;

@:final @:coreApi class Array<T> implements ArrayAccess<T>
{
	public var length(default,null) : Int;
	//private var __a:FixedArray<T>;
	
	private var __a:Pointer<T>;
	private var __byte_length:Int;
	
	@:keep private static function __alloc_mem<T>(len:Int,obsz:Int):Pointer<T>{
		var p:Pointer<Char> = cast c.CStdlib.calloc(len, obsz);
		return cast p;
	}
	
	@:extern private static inline function memcpy<T>(src:FixedArray<T>, srcPos:Int, dest:FixedArray<T>, destPos:Int, length:Int):Void
	{
		FixedArray.copy(src.array, srcPos, dest.array, destPos, length);
	}

	private static function __new<T>(len:Int):Array<T> {
		var ret = new Array();
		ret.__a = __alloc_mem(len,Lib.sizeof(new TypeReference<Pointer<Char>>()));
		ret.__byte_length = len;
		return cast ret;
	}

	public function new() : Void
	{
		this.length = 0;
		this.__a = cast __alloc_mem(1,8); // TODO: fix wasting the allocation
		this.__byte_length = 1;      //
	}

	@:keep private static function ofNative<X>(native:FixedArray<X>):Array<X>
	{
		var ret = new Array();
		ret.__a = cast native.array;
		ret.length = native.length;
		return ret;
	}
	
	public function concat( a : Array<T> ) : Array<T>
	{
		return null;
	}

	private function concatNative( a : FixedArray<T> ) : Void
	{

	}

	public function join( sep : String ) : String
	{
		// var buf = new StringBuf();
		// var i = -1;

		// var first = true;
		// var length = length;
		// while (++i < length)
		// {
		// 	if (first)
		// 		first = false;
		// 	else
		// 		buf.add(sep);
		// 	buf.add(__a.array[i]);
		// }

		// return buf.toString();
		return null; //TODO
	}

	public function pop() : Null<T>
	{
		return null;
	}

	public function push(x : T) : Int
	{
		return 0;
	}

	public function reverse() : Void
	{
		
	}

	public function shift() : Null<T>
	{
		return null;
	}

	public function slice( pos : Int, ?end : Int ) : Array<T>
	{
		return null;
	}

	public function sort( f : T -> T -> Int ) : Void
	{
		//TODO
	// 	if (length == 0)
	// 		return;
	// 	quicksort(0, length - 1, f);
	}
//
// 	private function quicksort( lo : Int, hi : Int, f : T -> T -> Int ) : Void
// 	{
//         var buf = __a;
// 		var i = lo, j = hi;
//         var p = buf[(i + j) >> 1];
// 		while ( i <= j )
// 		{
// 			while ( f(buf[i], p) < 0 ) i++;
//             while ( f(buf[j], p) > 0 ) j--;
// 			if ( i <= j )
// 			{
//                 var t = buf[i];
//                 buf[i++] = buf[j];
//                 buf[j--] = t;
//             }
// 		}
//
// 		if( lo < j ) quicksort( lo, j, f );
//         if( i < hi ) quicksort( i, hi, f );
// 	}

	public function splice( pos : Int, len : Int ) : Array<T>
	{
		return null;
	}

	private function spliceVoid( pos : Int, len : Int ) : Void
	{

	}

	public function toString() : String
	{
		return "TODO";
		// var ret = new StringBuf();
		// var a = __a;
		// ret.add("[");
		// var first = true;
		// for (i in 0...length)
		// {
		// 	if (first)
		// 		first = false;
		// 	else
		// 		ret.add(",");
		// 	ret.add(a.array[i]);
		// }

		// ret.add("]");
		// return ret.toString();
	}

	public function unshift( x : T ) : Void
	{

	}

	public function insert( pos : Int, x : T ) : Void
	{

	}

	public function remove( x : T ) : Bool
	{
		return false;
	}

	public function copy() : Array<T>
	{
		return null;
	}

	public function iterator() : Iterator<T>
	{
		return null;
	}
	
	private function iterator_64():Iterator<T> {
		var __a:Pointer<c.NInt.Int64> = cast __a;
		var i = 0;
		var len = length;
		return {
			hasNext:function() return i < len,
			next:function() {
				i = i + 1;
				return cast __a[i - 1];
			}
		};
	}

	public function map<S>( f : T -> S ) : Array<S> {
		return null; //TODO
		// var ret = [];
		// for (elt in this)
		// 	ret.push(f(elt));
		// return ret;
	}

	public function filter( f : T -> Bool ) : Array<T> {
		return null; //TODO
		// var ret = [];
		// for (elt in this)
		// 	if (f(elt))
		// 		ret.push(elt);
		// return ret;
	}

	@:keep private function __get(idx:Int):T
	{
		return cast null;
	}

	@:keep private function __set(idx:Int, v:T):T
	{
		return null;
	}

	private inline function __unsafe_get(idx:Int):T
	{
		return cast null;
	}

	private inline function __unsafe_set(idx:Int, val:T):T
	{
		return cast null;
	}
	
	
	
	@:keep private static function ofNative_8(native:Pointer<Char>,length:Int):Array<Char>
	{
		var ret    = new Array();
		ret.__a    = native;
		ret.length = length;
		return ret;
	}
	
	@:keep private function __alloc_mem_8(len:Int):Pointer<Char>{
		var p:Pointer<Char> = cast c.CStdlib.calloc(len, 1);
		return p;
	}
	
	private inline function memcpy_8(src:Pointer<Char>, srcPos:Int, dest:Pointer<Char>, destPos:Int, length:Int):Void{
		c.CString.memcpy((dest + destPos), (src + srcPos), length << 0 );
	}
	
	private function concat_8( a : Array<Char> ) : Array<Char>
	{
		var length = length;
		var len = length + a.length;
		var retarr = __alloc_mem_8(len);
		__byte_length = len;
		var __a:Pointer<Char> = cast __a;
		memcpy_8(cast __a, 0, cast retarr, 0, length);
		memcpy_8(cast a.__a, 0, cast retarr, length, a.length);

		return cast ofNative_8(cast retarr,len);
	}


	private function pop_8() : Null<T>
	{
		var __a:Pointer<Char> = cast __a;
		var length = length;
		if (length > 0)
		{
			length-=1;
			var val = cast __a[length];
			__a[length] = cast 0;
			this.length = length;

			return cast val;
		} else {
			return null;
		}
	}

	private function push_8(x : Char) : Int
	{
		var __a:Pointer<Char> = cast __a;
		var length = length;
		if (length >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			var newarr = __alloc_mem_8(newLen);
			memcpy_8(__a, 0, newarr, 0, length);
			__byte_length = newLen;
			__a = newarr;
			__a[length] = cast x;
			
			this.__a = cast newarr;
		} else {
	        __a[length] = cast x;
		}
		return ++this.length;
	}

	private function reverse_8() : Void
	{
		var i = 0;
		var l = this.length;
		var a = this.__a;
		var __a:Pointer<Char> = cast __a;
		var half = l >> 1;
		l -= 1;
		while ( i < half )
		{
			var tmp = __a[i];
			__a[i] = __a[l-i];
			__a[l-i] = tmp;
			i += 1;
		}
	}

	private function shift_8() : Null<T>
	{
		var l = this.length;
		if( l == 0 )
			return null;

		var __a:Pointer<Char> = cast __a;
		var x = __a[0];
		l -= 1;
		CString.memmove(__a, __a+1, l << 0);
		//memcpy_8(__a, 1, __a, 0, length-1);
		
		__a[l] = cast 0;
		this.length = l;
		return cast x;
	}

	private function slice_8( pos : Int, ?end : Int ) : Array<Char>
	{
		if( pos < 0 ){
			pos = this.length + pos;
			if( pos < 0 )
				pos = 0;
		}
		if( end == null )
			end = this.length;
		else if( end < 0 )
			end = this.length + end;
		if( end > this.length )
			end = this.length;
		var len = end - pos;
		if ( len < 0 ) return new Array();

		var newarr    = __alloc_mem_8(len);
		//__byte_length = len;
		var __a:Pointer<Char> = cast __a;
		memcpy_8(__a, pos, newarr, 0, len);

		return cast ofNative_8(newarr,len);
	}
	
	private function splice_8( pos : Int, len : Int ) : Array<Char>
	{
		if( len < 0 ) return __new_8(1);
		if( pos < 0 ) {
			pos = this.length + pos;
			if( pos < 0 ) pos = 0;
		}
		if( pos > this.length ) {
			pos = 0;
			len = 0;
		} else if( pos + len > this.length ) {
			len = this.length - pos;
			if( len < 0 ) len = 0;
		}
		var a:Pointer<Char> = cast this.__a;

		var ret = __alloc_mem_8(len);
		
		memcpy_8(a, pos, ret, 0, len);
		
		var ret = ofNative_8(ret,len);
		ret.__byte_length = len;
		
		var end = pos + len;
		memcpy_8(a, end, a, pos, this.length - end);
		this.length -= len;
		while( --len >= 0 )
			a[this.length + len] = cast 0;
		return cast ret;
	}
	
	private function unshift_8( x : Char ) : Void
	{
		var __a:Pointer<Char> = cast this.__a;
		var length = length;
		if (length >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			var newarr = __alloc_mem_8(newLen);
			memcpy_8(__a, 0, newarr, 1, length);
			__byte_length = newLen;
			__a = newarr;
			
			this.__a = cast newarr;
		} else {
			CString.memmove(__a, __a+1, length << 0);
		}

		this.__a[0] = cast x;
		++this.length;
	}

	private function insert_8( pos : Int, x : Char ) : Void
	{
		var l = this.length;
		if( pos < 0 ) {
			pos = l + pos;
			if( pos < 0 ) pos = 0;
		}
		if ( pos >= l ) {
			this.push_8(x);
			return;
		} else if (pos == 0) {
			this.unshift_8(x);
			return;
		}
		
		var __a:Pointer<Char> = cast __a;
		
		if (l >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			//var newarr = new FixedArray(newLen);
			var newarr = __alloc_mem_8(newLen);
			__byte_length = newLen;
			memcpy_8(__a, 0, newarr, 0, pos);
			newarr[pos] = cast x;
			memcpy_8(__a, pos, newarr, pos + 1, l - pos);

			this.__a = cast newarr;
			++this.length;
		} else {
			CString.memmove(__a+pos, __a+pos+1, (l-pos) << 0);
			__a[pos] = cast x;
			++this.length;
		}
	}
	
	private function copy_8() : Array<Char>
	{
		var len = length;
		var __a:Pointer<Char> = cast __a;
		var newarr = __alloc_mem_8(len);
		memcpy_8(__a, 0, newarr, 0, len);
		var ret = ofNative_8(newarr,len);
		ret.__byte_length = len;
		return cast ret;
	}
	
	private function remove_8( x : Char ) : Bool
	{
		var __a:Pointer<Char> = cast __a;
		var i = -1;
		var length = length;
		while (++i < length)
		{
			if (__a[i] == cast x)
			{
				memcpy_8(__a, i + 1, __a, i, length - i - 1);
				this.length-=1;
				__a[this.length] = cast 0;

				return true;
			}
		}

		return false;
	}
	
	@:keep private function __get_8(idx:Int):Char
	{
		var __a:Pointer<Char> = cast __a;
		if (idx >= length || idx < 0)
			return 0;

		return __a[idx];
	}

	@:keep private function __set_8(idx:Int, v:Char):Char
	{
		var __a:Pointer<Char> = cast __a;
		
		if (idx >= __byte_length)
		{
			var newl = idx + 1;
			if (idx == __byte_length)
				newl = (idx << 1) + 1;
			var newArr = __alloc_mem_8(newl);
			__byte_length = newl;
			if (length > 0)
				memcpy_8(__a, 0, newArr, 0, length);
			this.__a = cast (__a = newArr);
		}

		if (idx >= length)
			this.length = idx + 1;

		return __a[idx] = v;
	}

	private inline function __unsafe_get_8(idx:Int):Char
	{
		var __a:Pointer<Char> = cast __a;
		return __a[idx];
	}

	private inline function __unsafe_set_8(idx:Int, val:Char):Char
	{
		var __a:Pointer<Char> = cast __a;
		return __a[idx] = val;
	}
	
	private static function __new_8<T>(len:Int):Array<Char> {
		var ret = new Array();
		ret.__a = ret.__alloc_mem_8(len);
		ret.__byte_length = len;
		return cast ret;
	}

	
	@:keep private static function ofNative_32(native:Pointer<Int>,length:Int):Array<Int>
	{
		var ret    = new Array();
		ret.__a    = native;
		ret.length = length;
		return ret;
	}
	
	@:keep inline private function __alloc_mem_32(len:Int):Pointer<Int>{
		var p:Pointer<Int> = cast c.CStdlib.calloc(len, 4);
		return p;
	}
	
	private inline function memcpy_32(src:Pointer<Int>, srcPos:Int, dest:Pointer<Int>, destPos:Int, length:Int):Void{
		c.CString.memcpy((dest + destPos), (src + srcPos), length << 2 );
	}
	
	private function concat_32( a : Array<Int> ) : Array<Int>
	{
		var length = length;
		var len = length + a.length;
		var retarr = __alloc_mem_32(len);
		__byte_length = len;
		var __a:Pointer<Int> = cast __a;
		memcpy_32(cast __a, 0, cast retarr, 0, length);
		memcpy_32(cast a.__a, 0, cast retarr, length, a.length);

		return cast ofNative_32(cast retarr,len);
	}


	private function pop_32() : Null<T>
	{
		var __a:Pointer<Int> = cast __a;
		var length = length;
		if (length > 0)
		{
			length-=1;
			var val = cast __a[length];
			__a[length] = cast 0;
			this.length = length;

			return cast val;
		} else {
			return null;
		}
	}

	private function push_32(x : Int) : Int
	{
		var __a:Pointer<Int> = cast __a;
		var length = length;
		if (length >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			var newarr = __alloc_mem_32(newLen);
			memcpy_32(__a, 0, newarr, 0, length);
			__byte_length = newLen;
			__a = newarr;
			__a[length] = cast x;
			
			this.__a = cast newarr;
		} else {
	        __a[length] = cast x;
		}
		return ++this.length;
	}

	private function reverse_32() : Void
	{
		var i = 0;
		var l = this.length;
		var a = this.__a;
		var __a:Pointer<Int> = cast __a;
		var half = l >> 1;
		l -= 1;
		while ( i < half )
		{
			var tmp = __a[i];
			__a[i] = __a[l-i];
			__a[l-i] = tmp;
			i += 1;
		}
	}

	private function shift_32() : Null<T>
	{
		var l = this.length;
		if( l == 0 )
			return null;

		var __a:Pointer<Int> = cast __a;
		var x = __a[0];
		l -= 1;
		CString.memmove(__a, __a+1, l << 2);
		//memcpy_32(__a, 1, __a, 0, length-1);
		
		__a[l] = cast 0;
		this.length = l;
		return cast x;
	}

	private function slice_32( pos : Int, ?end : Int ) : Array<Int>
	{
		if( pos < 0 ){
			pos = this.length + pos;
			if( pos < 0 )
				pos = 0;
		}
		if( end == null )
			end = this.length;
		else if( end < 0 )
			end = this.length + end;
		if( end > this.length )
			end = this.length;
		var len = end - pos;
		if ( len < 0 ) return new Array();

		var newarr    = __alloc_mem_32(len);
		//__byte_length = len;
		var __a:Pointer<Int> = cast __a;
		memcpy_32(__a, pos, newarr, 0, len);

		return cast ofNative_32(newarr,len);
	}
	
	private function splice_32( pos : Int, len : Int ) : Array<Int>
	{
		if( len < 0 ) return __new_32(1);
		if( pos < 0 ) {
			pos = this.length + pos;
			if( pos < 0 ) pos = 0;
		}
		if( pos > this.length ) {
			pos = 0;
			len = 0;
		} else if( pos + len > this.length ) {
			len = this.length - pos;
			if( len < 0 ) len = 0;
		}
		var a:Pointer<Int> = cast this.__a;

		var ret = __alloc_mem_32(len);
		
		memcpy_32(a, pos, ret, 0, len);
		
		var ret = ofNative_32(ret,len);
		ret.__byte_length = len;
		
		var end = pos + len;
		memcpy_32(a, end, a, pos, this.length - end);
		this.length -= len;
		while( --len >= 0 )
			a[this.length + len] = cast 0;
		return cast ret;
	}
	
	private function unshift_32( x : Int ) : Void
	{
		var __a:Pointer<Int> = cast this.__a;
		var length = length;
		if (length >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			var newarr = __alloc_mem_32(newLen);
			memcpy_32(__a, 0, newarr, 1, length);
			__byte_length = newLen;
			__a = newarr;
			
			this.__a = cast newarr;
		} else {
			CString.memmove(__a, __a+1, length << 2);
		}

		this.__a[0] = cast x;
		++this.length;
	}

	private function insert_32( pos : Int, x : Int ) : Void
	{
		var l = this.length;
		if( pos < 0 ) {
			pos = l + pos;
			if( pos < 0 ) pos = 0;
		}
		if ( pos >= l ) {
			this.push_32(x);
			return;
		} else if (pos == 0) {
			this.unshift_32(x);
			return;
		}
		
		var __a:Pointer<Int> = cast __a;
		
		if (l >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			//var newarr = new FixedArray(newLen);
			var newarr = __alloc_mem_32(newLen);
			__byte_length = newLen;
			memcpy_32(__a, 0, newarr, 0, pos);
			newarr[pos] = cast x;
			memcpy_32(__a, pos, newarr, pos + 1, l - pos);

			this.__a = cast newarr;
			++this.length;
		} else {
			CString.memmove(__a+pos, __a+pos+1, (l-pos) << 2);
			__a[pos] = cast x;
			++this.length;
		}
	}
	
	private function copy_32() : Array<Int>
	{
		var len = length;
		var __a:Pointer<Int> = cast __a;
		var newarr = __alloc_mem_32(len);
		memcpy_32(__a, 0, newarr, 0, len);
		var ret = ofNative_32(newarr,len);
		ret.__byte_length = len;
		return cast ret;
	}
	
	private function remove_32( x : Int ) : Bool
	{
		var __a:Pointer<Int> = cast __a;
		var i = -1;
		var length = length;
		while (++i < length)
		{
			if (__a[i] == cast x)
			{
				memcpy_32(__a, i + 1, __a, i, length - i - 1);
				this.length-=1;
				__a[this.length] = cast 0;

				return true;
			}
		}

		return false;
	}
	
	@:keep private function __get_32(idx:Int):Int
	{
		var __a:Pointer<Int> = cast __a;
		if (idx >= length || idx < 0)
			return 0;

		return __a[idx];
	}

	@:keep private function __set_32(idx:Int, v:Int):Int
	{
		var __a:Pointer<Int> = cast __a;
		
		if (idx >= __byte_length)
		{
			var newl = idx + 1;
			if (idx == __byte_length)
				newl = (idx << 1) + 1;
			var newArr = __alloc_mem_32(newl);
			__byte_length = newl;
			if (length > 0)
				memcpy_32(__a, 0, newArr, 0, length);
			this.__a = cast (__a = newArr);
		}

		if (idx >= length)
			this.length = idx + 1;

		return __a[idx] = v;
	}

	private inline function __unsafe_get_32(idx:Int):Int
	{
		var __a:Pointer<Int> = cast __a;
		return __a[idx];
	}

	private inline function __unsafe_set_32(idx:Int, val:Int):Int
	{
		var __a:Pointer<Int> = cast __a;
		return __a[idx] = val;
	}
	
	private static function __new_32<T>(len:Int):Array<Int> {
		var ret = new Array();
		ret.__a = ret.__alloc_mem_32(len);
		ret.__byte_length = len;
		return cast ret;
	}

	
	@:keep private static function ofNative_64(native:Pointer<c.NInt.Int64>,length:Int):Array<c.NInt.Int64>
	{
		var ret    = new Array();
		ret.__a    = native;
		ret.length = length;
		return ret;
	}
	
	@:keep inline private function __alloc_mem_64(len:Int):Pointer<c.NInt.Int64>{
		var p:Pointer<c.NInt.Int64> = cast c.CStdlib.calloc(len, 8);
		return p;
	}
	
	private inline function memcpy_64(src:Pointer<c.NInt.Int64>, srcPos:Int, dest:Pointer<c.NInt.Int64>, destPos:Int, length:Int):Void{
		c.CString.memcpy((dest + destPos), (src + srcPos), length << 3 );
	}
	
	private function concat_64( a : Array<c.NInt.Int64> ) : Array<c.NInt.Int64>
	{
		var length = length;
		var len = length + a.length;
		var retarr = __alloc_mem_64(len);
		__byte_length = len;
		var __a:Pointer<c.NInt.Int64> = cast __a;
		memcpy_64(cast __a, 0, cast retarr, 0, length);
		memcpy_64(cast a.__a, 0, cast retarr, length, a.length);

		return cast ofNative_64(cast retarr,len);
	}


	private function pop_64() : Null<T>
	{
		var __a:Pointer<c.NInt.Int64> = cast __a;
		var length = length;
		if (length > 0)
		{
			length-=1;
			var val = cast __a[length];
			__a[length] = cast 0;
			this.length = length;

			return cast val;
		} else {
			return null;
		}
	}

	private function push_64(x : c.NInt.Int64) : Int
	{
		var __a:Pointer<c.NInt.Int64> = cast __a;
		var length = length;
		if (length >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			var newarr = __alloc_mem_64(newLen);
			memcpy_64(__a, 0, newarr, 0, length);
			__byte_length = newLen;
			__a = newarr;
			__a[length] = cast x;
			
			this.__a = cast newarr;
		} else {
	        __a[length] = cast x;
		}
		return ++this.length;
	}

	private function reverse_64() : Void
	{
		var i = 0;
		var l = this.length;
		var a = this.__a;
		var __a:Pointer<c.NInt.Int64> = cast __a;
		var half = l >> 1;
		l -= 1;
		while ( i < half )
		{
			var tmp = __a[i];
			__a[i] = __a[l-i];
			__a[l-i] = tmp;
			i += 1;
		}
	}

	private function shift_64() : Null<T>
	{
		var l = this.length;
		if( l == 0 )
			return null;

		var __a:Pointer<c.NInt.Int64> = cast __a;
		var x = __a[0];
		l -= 1;
		CString.memmove(__a, __a+1, l << 3);
		//memcpy_64(__a, 1, __a, 0, length-1);
		
		__a[l] = cast 0;
		this.length = l;
		return cast x;
	}

	private function slice_64( pos : Int, ?end : Int ) : Array<c.NInt.Int64>
	{
		if( pos < 0 ){
			pos = this.length + pos;
			if( pos < 0 )
				pos = 0;
		}
		if( end == null )
			end = this.length;
		else if( end < 0 )
			end = this.length + end;
		if( end > this.length )
			end = this.length;
		var len = end - pos;
		if ( len < 0 ) return new Array();

		var newarr    = __alloc_mem_64(len);
		//__byte_length = len;
		var __a:Pointer<c.NInt.Int64> = cast __a;
		memcpy_64(__a, pos, newarr, 0, len);

		return cast ofNative_64(newarr,len);
	}
	
	private function splice_64( pos : Int, len : Int ) : Array<c.NInt.Int64>
	{
		if( len < 0 ) return __new_64(1);
		if( pos < 0 ) {
			pos = this.length + pos;
			if( pos < 0 ) pos = 0;
		}
		if( pos > this.length ) {
			pos = 0;
			len = 0;
		} else if( pos + len > this.length ) {
			len = this.length - pos;
			if( len < 0 ) len = 0;
		}
		var a:Pointer<c.NInt.Int64> = cast this.__a;

		var ret = __alloc_mem_64(len);
		
		memcpy_64(a, pos, ret, 0, len);
		
		var ret = ofNative_64(ret,len);
		ret.__byte_length = len;
		
		var end = pos + len;
		memcpy_64(a, end, a, pos, this.length - end);
		this.length -= len;
		while( --len >= 0 )
			a[this.length + len] = cast 0;
		return cast ret;
	}
	
	private function unshift_64( x : c.NInt.Int64 ) : Void
	{
		var __a:Pointer<c.NInt.Int64> = cast this.__a;
		var length = length;
		if (length >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			var newarr = __alloc_mem_64(newLen);
			memcpy_64(__a, 0, newarr, 1, length);
			__byte_length = newLen;
			__a = newarr;
			
			this.__a = cast newarr;
		} else {
			CString.memmove(__a, __a+1, length << 3);
		}

		this.__a[0] = cast x;
		++this.length;
	}

	private function insert_64( pos : Int, x : c.NInt.Int64 ) : Void
	{
		var l = this.length;
		if( pos < 0 ) {
			pos = l + pos;
			if( pos < 0 ) pos = 0;
		}
		if ( pos >= l ) {
			this.push_64(x);
			return;
		} else if (pos == 0) {
			this.unshift_64(x);
			return;
		}
		
		var __a:Pointer<c.NInt.Int64> = cast __a;
		
		if (l >= __byte_length)
		{
			var newLen = (length << 1) + 1;
			//var newarr = new FixedArray(newLen);
			var newarr = __alloc_mem_64(newLen);
			__byte_length = newLen;
			memcpy_64(__a, 0, newarr, 0, pos);
			newarr[pos] = cast x;
			memcpy_64(__a, pos, newarr, pos + 1, l - pos);

			this.__a = cast newarr;
			++this.length;
		} else {
			CString.memmove(__a+pos, __a+pos+1, (l-pos) << 3);
			__a[pos] = cast x;
			++this.length;
		}
	}
	
	private function copy_64() : Array<c.NInt.Int64>
	{
		var len = length;
		var __a:Pointer<c.NInt.Int64> = cast __a;
		var newarr = __alloc_mem_64(len);
		memcpy_64(__a, 0, newarr, 0, len);
		var ret = ofNative_64(newarr,len);
		ret.__byte_length = len;
		return cast ret;
	}
	
	private function remove_64( x : c.NInt.Int64 ) : Bool
	{
		var __a:Pointer<c.NInt.Int64> = cast __a;
		var i = -1;
		var length = length;
		while (++i < length)
		{
			if (__a[i] == cast x)
			{
				memcpy_64(__a, i + 1, __a, i, length - i - 1);
				this.length-=1;
				__a[this.length] = cast 0;

				return true;
			}
		}

		return false;
	}
	
	@:keep private function __get_64(idx:Int):c.NInt.Int64
	{
		var __a:Pointer<c.NInt.Int64> = cast __a;
		if (idx >= length || idx < 0)
			return 0;

		return __a[idx];
	}

	@:keep private function __set_64(idx:Int, v:c.NInt.Int64):c.NInt.Int64
	{
		var __a:Pointer<c.NInt.Int64> = cast __a;
		
		if (idx >= __byte_length)
		{
			var newl = idx + 1;
			if (idx == __byte_length)
				newl = (idx << 1) + 1;
			var newArr = __alloc_mem_64(newl);
			__byte_length = newl;
			if (length > 0)
				memcpy_64(__a, 0, newArr, 0, length);
			this.__a = cast (__a = newArr);
		}

		if (idx >= length)
			this.length = idx + 1;

		return __a[idx] = v;
	}

	private inline function __unsafe_get_64(idx:Int):c.NInt.Int64
	{
		var __a:Pointer<c.NInt.Int64> = cast __a;
		return __a[idx];
	}

	private inline function __unsafe_set_64(idx:Int, val:c.NInt.Int64):c.NInt.Int64
	{
		var __a:Pointer<c.NInt.Int64> = cast __a;
		return __a[idx] = val;
	}
	
	private static function __new_64<T>(len:Int):Array<c.NInt.Int64> {
		var ret = new Array();
		ret.__a = ret.__alloc_mem_64(len);
		ret.__byte_length = len;
		return cast ret;
	}


	
	
}
