int main1(int a,int b,int m,int p){
  int t, j, e, o, v;

  t=69;
  j=t;
  e=p;
  o=j;
  v=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j <= t;
  loop invariant e >= p;
  loop invariant (e - p) % 5 == 0;
  loop invariant p == \at(p,Pre);
  loop invariant e == p + 5*(j - t);
  loop invariant o == t + (j - t)*p + 5*(j - t)*(j - t + 1)/2;
  loop invariant e == \at(p,Pre) + 5*(j - 69);
  loop invariant o == 69 + \at(p,Pre)*(j - 69) + 5*(j - 69)*(j - 68)/2;
  loop invariant (j - t) <= 1;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant o == t + (j - t)*p + 5*((j - t)*(j - t + 1)/2);
  loop assigns e, j, o;
*/
while (1) {
      if (j>=t) {
          break;
      }
      e = e+3;
      j = j+1;
      e = e+2;
      o = o+e;
  }

}
