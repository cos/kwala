package particles;
public class Particle {
	Particle next;
	private void foo() {
		Particle p = new Particle();
		Particle q = new Particle();
		p.next = q;
	}
}
