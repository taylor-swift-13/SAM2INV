int main1(int n,int w){
  int t;
  t=(w%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*t + n - \at(n,Pre) == 2*( (\at(w,Pre) % 20) + 5 );
  loop invariant (n - \at(n,Pre)) % 2 == 0;
  loop invariant n == \at(n,Pre) + 2*( (\at(w,Pre)%20) + 5 - t );
  loop invariant t <= ((\at(w, Pre) % 20) + 5);
  loop invariant w >= \at(w, Pre);
  loop invariant n + 2*t == \at(n, Pre) + 2*((\at(w, Pre) % 20) + 5);
  loop invariant n >= \at(n, Pre);
  loop invariant ((n - \at(n, Pre)) % 2 == 0);
  loop invariant n - \at(n,Pre) == 2 * ( ((\at(w,Pre) % 20) + 5) - t );
  loop assigns t, n, w;
*/
while (1) {
      if (!(t>0)) {
          break;
      }
      t = t - 1;
      n += 2;
      w += t;
  }
}