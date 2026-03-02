int main1(int a,int b){
  int i, v, p, m;

  i=20;
  v=0;
  p=i;
  m=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 0;
  loop invariant p == 20;
  loop invariant v == 0;
  loop invariant i == 20;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant p == 20 && m == 0 && i == 20;
  loop invariant v == 0 && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant m == 0 && p == 20 && i == 20;
  loop invariant a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant v < i/2;
  loop invariant p == i;
  loop invariant m == 0 && v == 0 && p == 20;
  loop invariant p == i && i == 20 && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant p == 20 && m == 0 && v == 0 && i == 20;
  loop assigns p, m;
*/
while (1) {
      if (v<i/2) {
          p = p+m;
      }
      else {
          p = p+1;
      }
      m = m+m;
  }

}
