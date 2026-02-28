int main1(int a,int n){
  int u, c, f, v;

  u=(a%23)+12;
  c=0;
  f=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant f <= u/2 ==> v == f*(f+3)/2;

  loop invariant (f <= u/2) ==> (v - f*(f - 1)/2 == 2*f);

  loop invariant u == (a % 23) + 12;
  loop invariant 0 <= f;

  loop invariant v >= 0;
  loop invariant v >= f*(f-1)/2;
  loop invariant u == (\at(a, Pre) % 23) + 12;

  loop invariant v >= (f * (f - 1)) / 2;
  loop invariant v <= (f * (f + 3)) / 2;
  loop assigns v, f;
*/
while (f<u) {
      if (f<u/2) {
          v = v+1;
      }
      else {
          v = v-1;
      }
      f = f+1;
      v = v+f;
  }

}
