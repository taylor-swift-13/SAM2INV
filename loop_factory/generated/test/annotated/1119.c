int main1(int i){
  int k, ga, fogf, w;
  k=54;
  ga=0;
  fogf=0;
  w=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= fogf <= k;
  loop invariant ga == i * fogf;
  loop invariant w == -8 + (fogf * (fogf + 1)) / 2;
  loop assigns fogf, ga, w;
*/
while (fogf<k) {
      ga = ga + i;
      fogf++;
      w += fogf;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ga == i * fogf) || (ga == 1);
  loop invariant k == 54;
  loop assigns fogf, ga, w;
*/
while (1) {
      if (!(ga>=2)) {
          break;
      }
      w = w+fogf*ga;
      fogf = fogf+(w%6);
      ga = 1;
  }
}