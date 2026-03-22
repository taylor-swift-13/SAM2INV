int main1(int d,int e){
  int tv, de, k, wj, lbb, ioo;
  tv=d;
  de=tv;
  k=e;
  wj=-2;
  lbb=tv;
  ioo=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (wj == -2 + (de - \at(d,Pre)));
  loop invariant (ioo == d * (de - \at(d,Pre)) + 2*(de - \at(d,Pre))*((de - \at(d,Pre)) + 1));
  loop invariant (tv == d);
  loop invariant (k - \at(e,Pre) == de - \at(d,Pre));
  loop invariant lbb == d + 4*(de - \at(d, Pre));
  loop invariant wj == -2 + (de - \at(d, Pre));
  loop invariant k  == \at(e, Pre) + (de - \at(d, Pre));
  loop invariant ioo == d*(de - \at(d, Pre)) + 2*(de - \at(d, Pre))*(de - \at(d, Pre)) + 2*(de - \at(d, Pre));
  loop invariant e   == \at(e, Pre) + ((de - \at(d, Pre))*(de - \at(d, Pre)) - 3*(de - \at(d, Pre))) / 2;
  loop invariant k - de == \at(e, Pre) - \at(d, Pre);
  loop invariant lbb == 4*de - 3*\at(d, Pre);
  loop invariant k - de == \at(e,Pre) - d;
  loop invariant de >= d;
  loop invariant wj >= -2;
  loop invariant lbb >= d;
  loop invariant de >= \at(d,Pre) &&
                   wj == -2 + (de - \at(d,Pre)) &&
                   lbb == \at(d,Pre) + 4*(de - \at(d,Pre)) &&
                   e == \at(e,Pre) + (((de - \at(d,Pre)) * ((de - \at(d,Pre)) - 3)) / 2) &&
                   ioo == (\at(d,Pre) * (de - \at(d,Pre))) + 2*(de - \at(d,Pre))*((de - \at(d,Pre)) + 1) &&
                   k == \at(e,Pre) + (de - \at(d,Pre));
  loop invariant de - \at(d,Pre) >= 0;
  loop assigns k, wj, lbb, e, ioo, de;
*/
while (1) {
      if (!(de-1>=0)) {
          break;
      }
      k = (1)+(k);
      wj = wj + 1;
      lbb += 4;
      e = e + wj;
      ioo += lbb;
      de = de + 1;
  }
}