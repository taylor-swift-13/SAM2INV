int main1(int v){
  int e7zt, b03, e, oc, ta3;
  e7zt=v+15;
  b03=0;
  e=e7zt;
  oc=v - 0;
  ta3=e7zt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == (e7zt + b03);
  loop invariant ta3 == (e7zt * (b03 + 1));
  loop invariant oc == (v - b03);
  loop invariant e7zt == (\at(v, Pre) + 15);
  loop invariant 0 <= b03;
  loop invariant (e7zt >= 0) ==> (b03 <= e7zt);
  loop assigns b03, oc, ta3, e;
*/
while (b03 < e7zt) {
      b03 += 1;
      oc = (v)+(-(b03));
      ta3 += e7zt;
      e += 1;
  }
}