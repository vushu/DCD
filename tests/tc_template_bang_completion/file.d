struct Wrapper(T) {
	T data;
}

class Something(T, X){
	this(T foo, X bar){}
}

void doSomething(T)(T someElement){

}

void instantiateTemp1() {
	Wrapper!
}

void instantiateTemp2() {
	Something!
}

void instantiateTemp3() {
	doSomething!
}

void instantiateTemp4() {
	doSomething!(
}

void instantiateTemp5() {
	doSomething!("something",
}

void instantiateTemp6() {
	Something!("something",
}

void shouldNotComplete1() {
	Something!!
}

void shouldNotComplete2() {
	Something!!(
}

void partlyInstatiated1() {
	Wrapper!string
}

void partlyInstatiated2() {
	Something!(string, int)(
}

void partlyInstatiated3() {
	doSomething!string(
}
