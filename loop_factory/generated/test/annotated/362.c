int main1(int e){
  int ff, ef, d, l1;
  ff=(e%20)+13;
  ef=ff;
  d=ff;
  l1=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ff == ((\at(e, Pre) % 20) + 13);
  loop invariant ef <= ff;
  loop invariant ff == (e % 20) + 13;
  loop assigns ef;
*/
for (; ef-1>=0; ef = ef - 1) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l1 >= -3;
  loop invariant d == ((\at(e, Pre) % 20) + 13);
  loop invariant e - d * l1 == \at(e,Pre) + 3*d;
  loop assigns e, ff, l1;
*/
while (ff>l1) {
      ff = ff - l1;
      e += d;
      l1 = (1)+(l1);
  }
}