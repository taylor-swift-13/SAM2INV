int main1(int a,int m){
  int d, w, o;

  d=a+19;
  w=0;
  o=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= w;
  loop invariant (d >= 0) ==> (w <= d);
  loop invariant o >= -1 && o <= -1 + 2*w;
  loop invariant d == \at(a, Pre) + 19;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);

  loop invariant (o + 1) % 2 == 0;

  loop invariant o >= -1;
  loop invariant o <= 2*w - 1;
  loop invariant o <= -1 + 2*w;
  loop assigns w, o;
*/
while (w<d) {
      if (w+6<=d+d) {
          o = o+2;
      }
      w = w+1;
  }

}
