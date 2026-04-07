int main1(){
  int w, e5d, z, l7, wi, yz, oyos, pay;
  w=1*5;
  e5d=0;
  z=9;
  l7=14;
  wi=0;
  yz=w;
  oyos=w;
  pay=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (z + l7) == 23;
  loop invariant yz == (w + e5d);
  loop invariant oyos == (w - (e5d / 2));
  loop invariant wi == (e5d % 2);
  loop invariant 0 <= e5d <= w;
  loop invariant pay >= w;
  loop invariant (w - e5d) <= oyos;
  loop invariant oyos <= w;
  loop assigns z, l7, wi, e5d, pay, oyos, yz;
*/
while (e5d<w) {
      if (wi==0) {
          z += 2;
          l7 -= 2;
          wi = 1;
      }
      else {
          z -= 2;
          l7 += 2;
          wi = 0;
      }
      e5d += 1;
      if (e5d+4<=oyos+w) {
          pay += oyos;
      }
      oyos = oyos+(e5d%2);
      yz = yz + 1;
      oyos = oyos - 1;
  }
}