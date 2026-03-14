int main1(int z){
  int za, ni, q, vy, p, g;
  za=z+23;
  ni=0;
  q=0;
  vy=0;
  p=0;
  g=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 7 + 10*(ni/5) + ((ni%5) * ((ni%5) - 1)) / 2;
  loop invariant 0 <= ni;
  loop invariant za == z + 23;
  loop assigns ni, vy, p, q, g;
*/
for (; ni<za; ni += 1) {
      vy = ni%5;
      if (!(!(ni>=g))) {
          p = (ni-g)%5;
          q = q+vy-p;
      }
      else {
          q = q + vy;
      }
      g = g + vy;
  }
}