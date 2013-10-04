@:keep
class A {
	var id:String;
	public function new(id = "A") this.id = id;
	public function a() return 'A.a (this=$id)';
	public function b() return 'A.b (this=$id)';
}

class B extends A {
	public function new(id = "B") super(id);
	public override function b() return 'B.b (this=$id)';
	public function c() return 'B.c (this=$id)';
}

class C extends B {
	public function new(id = "C") super(id);
	public override function b() return 'C.b (this=$id)';
}

class D extends C {
	public function new(id = "D") super(id);
	public function d() return 'D.d (this=$id)';
}

class E extends D {
	public function new() super("E");
	public override function b() return 'E.b (this=$id) ' + super.b();
}

class TestVTable {
	public static function run(){
		var d = new D();
		Main.equals("A.a (this=D)", d.a());
		Main.equals("C.b (this=D)", d.b()); // FAILS if E is compiled
		Main.equals("B.c (this=D)", d.c());
		Main.equals("D.d (this=D)", d.d());
		
		var d:A = new D();
		Main.equals("A.a (this=D)", d.a());
		Main.equals("C.b (this=D)", d.b()); // FAILS if E is compiled
		
		var c = new C();
		Main.equals("A.a (this=C)", c.a());
		Main.equals("C.b (this=C)", c.b());
		Main.equals("B.c (this=C)", c.c());
		
		var e = new E();
		Main.equals("E.b (this=E) C.b (this=E)", e.b());
		
		var e:B = new E();
		Main.equals("E.b (this=E) C.b (this=E)", e.b());
	}
}