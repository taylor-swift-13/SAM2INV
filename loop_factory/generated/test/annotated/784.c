int main1(int w,int u){
  int cc3o, o7;
  cc3o=(w%7)+9;
  o7=cc3o+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cc3o == (w % 7) + 9;
  loop invariant 0 <= o7 - cc3o;
  loop invariant o7 - cc3o <= 3;
  loop invariant cc3o == (\at(w, Pre) % 7) + 9;
  loop assigns o7;
*/
for (; o7>=cc3o+1; o7 -= 1) {
  }
}