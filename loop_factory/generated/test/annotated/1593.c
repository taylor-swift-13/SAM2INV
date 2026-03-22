int main1(int z){
  int m8b, lg, w, vh, h3, st, xu;
  m8b=z+25;
  lg=0;
  w=22;
  vh=0;
  h3=1;
  st=0;
  xu=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m8b == \at(z, Pre) + 25;
  loop invariant xu == -6 + 4 * lg;
  loop invariant 1 + lg <= h3;
  loop invariant h3 <= 1 + 2 * lg;
  loop invariant w + vh == 22;
  loop invariant st <= h3;
  loop invariant 0 <= w;
  loop invariant 0 <= lg;
  loop invariant vh >= 0;
  loop invariant z >= \at(z, Pre);
  loop assigns st, vh, w, h3, lg, z, xu;
*/
while (w>0&&lg<m8b) {
      if (w<h3) {
          st = w;
      }
      else {
          st = h3;
      }
      vh = vh + st;
      w = w - st;
      if (lg%2==0) {
          h3 += 2;
      }
      else {
          h3 += 1;
      }
      lg++;
      z = z + w;
      xu = xu + 3;
      xu = xu + 1;
  }
}