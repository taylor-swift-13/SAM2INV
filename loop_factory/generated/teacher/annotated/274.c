int main1(int a,int b){
  int t, w, x;

  t=24;
  w=0;
  x=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant t == 24;
  loop invariant w == 0;
  loop invariant x >= 1;
  loop invariant w <= t;
  loop invariant x % 9 == 1;
  loop invariant 0 <= w;
  loop assigns x;
*/
while (w<t) {
      x = x+4;
      x = x+x;
  }

}
