int main1(int g,int a){
  int e2v8, e6;
  e2v8=a+24;
  e6=e2v8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(g, Pre) + a * ( \at(a, Pre) + 24 - e6 );
  loop invariant e2v8 == a + 24;
  loop invariant e6 <= (\at(a, Pre) + 24);
  loop invariant e2v8 == \at(a,Pre) + 24;
  loop assigns g, e6;
*/
for (; e6>=1; e6 = e6 - 1) {
      g = g + a;
  }
}