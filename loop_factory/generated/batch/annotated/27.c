int main1(int m,int n){
  int b, f, v;

  b=69;
  f=0;
  v=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 69;
  loop invariant 0 <= f && f <= b;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant f == 0 ==> v == -2;
  loop invariant 0 <= f;
  loop invariant f <= b;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop assigns f, v;
*/
while (f<b) {
      if (f+1<=n+b) {
          v = v+v;
      }
      else {
          v = b+v;
      }
      f = f+1;
  }

}
