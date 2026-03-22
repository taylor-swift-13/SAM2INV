int main1(int a){
  int od9, mi, iso, tkm, f89, l7;
  od9=a-5;
  mi=od9;
  iso=2;
  tkm=0;
  f89=mi;
  l7=a*3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant od9 == \at(a, Pre) - 5;
  loop invariant iso == 2;
  loop invariant tkm == iso * (a - \at(a, Pre));
  loop invariant mi >= od9;
  loop invariant a >= \at(a, Pre);
  loop invariant f89 >= \at(a, Pre) - 5;
  loop invariant a == \at(a, Pre) + (mi - od9) * od9 + ((mi - od9) * (mi - od9 - 1)) / 2;
  loop invariant tkm == iso * ((mi - od9) * od9 + ((mi - od9) * (mi - od9 - 1)) / 2);
  loop invariant tkm == 2*(mi - od9)*od9 + (mi - od9)*(mi - od9 - 1);
  loop invariant a == \at(a, Pre)
                   + (mi - (\at(a, Pre) - 5)) * (\at(a, Pre) - 5)
                   + ((mi - (\at(a, Pre) - 5)) * (mi - (\at(a, Pre) - 5) - 1)) / 2;
  loop invariant tkm == (mi - (\at(a, Pre) - 5)) * (2*(\at(a, Pre) - 5) + (mi - (\at(a, Pre) - 5)) - 1);
  loop invariant mi - (\at(a, Pre) - 5) >= 0;
  loop assigns tkm, a, f89, mi;
*/
while (mi-1>=0) {
      tkm = tkm+iso*mi;
      a += mi;
      f89 = f89+(tkm%7);
      mi++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant od9 == \at(a, Pre) - 5;
  loop invariant mi <= od9;
  loop assigns l7, tkm, iso, mi;
*/
while (mi<od9) {
      l7 += tkm;
      tkm = tkm + l7;
      iso = iso + l7;
      mi = od9;
  }
}