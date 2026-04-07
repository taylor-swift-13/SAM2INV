int main1(){
  int n, vv0, cqb, bo8x, wvo, dq7l, z, b5m;
  n=(1%12)+16;
  vv0=0;
  cqb=0;
  bo8x=0;
  wvo=0;
  dq7l=0;
  z=0;
  b5m=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= cqb <= vv0;
  loop invariant 0 <= wvo;
  loop invariant 0 <= bo8x;
  loop invariant 0 <= vv0 <= (n + 1);
  loop invariant 0 <= b5m <= 10 * vv0;
  loop invariant z >= vv0;
  loop invariant 0 <= dq7l <= vv0;
  loop invariant z <= 4 * vv0;
  loop invariant wvo <= (vv0 * (vv0 + 1)) / 2;
  loop invariant bo8x <= (vv0 * (vv0 + 1) * (vv0 + 2)) / 6;
  loop assigns vv0, b5m, z, bo8x, wvo, cqb, dq7l;
*/
while (vv0<n+(1%7)) {
      if (!(!(vv0%11==0))) {
          if (vv0%8==0) {
              bo8x++;
              z += 2;
          }
          else {
              if (vv0%7==0) {
                  wvo = wvo + 1;
                  z = z + 3;
              }
              else {
                  if (1) {
                      dq7l++;
                      z += 4;
                  }
              }
          }
      }
      else {
          cqb++;
          z += 1;
      }
      vv0 += 1;
      b5m = b5m+vv0%11;
      bo8x += wvo;
      wvo += cqb;
  }
}