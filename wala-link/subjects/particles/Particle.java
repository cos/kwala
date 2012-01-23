package particles;
public class Particle {
	Particle next;
	private void foo() {
		Particle p = new Particle();
		Particle q = new Particle();
		p.next = q;
	}
	
	public static void main(String[] args) {
		Particle p = new Particle();
		p.foo();
	}
}