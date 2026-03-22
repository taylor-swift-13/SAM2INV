int main1(){
  int e6p, no, i, kj3;
  e6p=91;
  no=0;
  i=0;
  kj3=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kj3 + no == 6;
  loop invariant e6p == 91;
  loop invariant i == (15 * no - no * no) / 2;
  loop invariant 0 <= no <= e6p;
  loop invariant 0 <= kj3;
  loop assigns no, i, kj3;
*/
while (no<e6p&&kj3>0) {
      no += 1;
      i += kj3;
      kj3--;
      i = i + 1;
  }
}