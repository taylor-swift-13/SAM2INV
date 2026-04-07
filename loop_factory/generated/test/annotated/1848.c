int main1(){
  int jx, ba, i1c, t6, a, ak, kx;
  jx=(1%11)+16;
  ba=0;
  i1c=ba;
  t6=0;
  a=6;
  ak=ba;
  kx=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i1c == t6;
  loop invariant kx == -4 + 3*ba;
  loop invariant ba <= jx;
  loop invariant 0 <= ba;
  loop invariant a == 6;
  loop invariant t6 == 2*ba;
  loop invariant ak == ba*(ba + 4);
  loop invariant jx == 17;
  loop assigns a, ak, ba, i1c, t6, kx;
*/
while (1) {
      if (a==jx+1) {
          i1c = i1c + 3;
          t6 = t6 + 3;
      }
      else {
          i1c += 2;
          t6 += 2;
      }
      if (a==jx) {
          i1c++;
          a++;
      }
      ak += t6;
      ak = ak + 3;
      kx = kx + 3;
      ba = ba + 1;
      if (!(!(ba>=jx))) {
          break;
      }
  }
}