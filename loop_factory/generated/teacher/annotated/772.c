int main1(int b,int p){
  int m, z, v, o;

  m=p;
  z=0;
  v=b;
  o=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*o - v*v == 3*\at(b, Pre) - (\at(b, Pre))*(\at(b, Pre));
  loop invariant p == \at(p, Pre);
  loop invariant m == p;
  loop invariant v >= \at(b, Pre);

  loop invariant o == b + 2*b*((v - b)/3) + 3*(((v - b)/3) * ((v - b)/3));
  loop invariant v >= b;
  loop invariant ((v - b) % 3 == 0);
  loop invariant 3*(o - \at(b, Pre)) == (v - \at(b, Pre))*(v + \at(b, Pre));
  loop invariant (v - \at(b, Pre)) >= 0;
  loop invariant ((v - \at(b, Pre)) % 3) == 0;
  loop invariant m == \at(p, Pre);
  loop invariant 3*(o - \at(b, Pre)) == v*v - \at(b, Pre)*\at(b, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant (v - \at(b, Pre)) % 3 == 0;
  loop assigns o, v;
*/
while (1) {
      o = o+v;
      v = v+3;
      o = o+v;
  }

}
