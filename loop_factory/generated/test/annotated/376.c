int main1(){
  int f, fn, no, aa1;
  f=(1%11)+11;
  fn=0;
  no=1;
  aa1=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aa1 == 3 + 2*fn;
  loop invariant no  == 1 + 2*fn;
  loop invariant 0 <= fn <= f;
  loop invariant f == (1%11) + 11;
  loop assigns fn, aa1, no;
*/
while (1) {
      if (!(fn<f)) {
          break;
      }
      fn += 1;
      aa1 += 2;
      no += 2;
  }
}