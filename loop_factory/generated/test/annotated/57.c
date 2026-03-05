int main1(int w){
  int equn, gh7k, c;
  equn=65;
  gh7k=0;
  c=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c;
  loop invariant c <= 2*equn - 1;
  loop invariant gh7k == 0;
  loop invariant w == \at(w, Pre);
  loop invariant equn == 65;
  loop invariant (c == 0) || (c % 2 == 1);
  loop assigns c, w;
*/
while (c<equn) {
      c = 2*c;
      c = c + 1;
      w = w + gh7k;
  }
}