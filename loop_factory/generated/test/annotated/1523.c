int main1(int b){
  int mm, a4l, j, fu, j6fc, vi, no, pd, s7z, ws;
  mm=13;
  a4l=0;
  j=13;
  fu=-2;
  j6fc=11;
  vi=-6;
  no=0;
  pd=a4l;
  s7z=0;
  ws=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= a4l <= mm;
  loop invariant a4l < mm;
  loop invariant j >= 13;
  loop invariant j6fc >= 11;
  loop invariant fu >= -2;
  loop invariant pd == 0;
  loop invariant vi >= -6 + a4l;
  loop invariant no == 0;
  loop invariant ws >= b + 7*a4l;
  loop assigns a4l, ws, j, fu, j6fc, s7z, vi;
*/
while (1) {
      if (a4l%5==1) {
          j++;
      }
      else {
          fu = fu + 1;
      }
      if (a4l%5==2) {
          j6fc++;
      }
      else {
      }
      ws += j;
      s7z = (s7z+fu)%3;
      s7z = vi+no+pd;
      vi++;
      if (a4l+2<=ws+mm) {
          ws = ws + vi;
      }
      else {
          vi = vi + 3;
      }
      a4l += 1;
      if (a4l>=mm) {
          break;
      }
  }
}