int main1(){
  int uv, jz, l70, eb92, eu;
  uv=1+16;
  jz=0;
  l70=-5;
  eb92=jz;
  eu=jz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((jz == 0) && (l70 == -5) && (eb92 == 0) && (eu == 0))
                   || ((jz == uv) && (l70 == 4) && (eb92 == 4) && (eu == 4));
  loop invariant (jz == 0) ==> (l70 == -5 && eb92 == 0 && eu == 0);
  loop invariant 0 <= jz;
  loop invariant jz <= uv;
  loop invariant eu >= eb92;
  loop invariant eb92 >= 0;
  loop invariant (jz == 0 && eu == 0 && eb92 == 0 && l70 == -5)
                   || (jz == uv && l70 == (-5 + 9) && eb92 == l70 && eu == eb92);
  loop invariant (jz == 0 && l70 == -5 && eb92 == 0 && eu == 0)
                   || (jz == uv && l70 == 4 && eb92 == 4 && eu == 4);
  loop assigns l70, eb92, eu, jz;
*/
while (jz<=uv-1) {
      l70 = l70 + 9;
      eb92 = eb92 + l70;
      eu += eb92;
      jz = uv;
  }
}