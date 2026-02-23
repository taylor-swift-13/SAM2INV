int main1(int a,int b){
  int t, w, x;

  t=24;
  w=0;
  x=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 24;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant w <= t;
  loop invariant w % 3 == 0;
  loop invariant x >= 1;
  loop invariant 0 <= w;
  loop invariant w <= t + 2;
  loop invariant x >= 1 && (t >= b+4 ==> x == 1);
  loop invariant (t >= b+4) ==> (x == 1);
  loop invariant w >= 0;
  loop assigns w, x;
*/
while (w<t) {
      if (t<b+4) {
          x = x+x;
      }
      w = w+3;
  }

}
