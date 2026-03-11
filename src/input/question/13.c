int main1(){
  int p6l, n80, p, vj;
  p6l=180;
  n80=3;
  p=1;
  vj=1;

while (n80<p6l) {
      if (!(p<11)) {
          vj = -1;
      }
      if (p<=1) {
          vj = 1;
      }
      n80++;
      p += vj;
  }
/*@
  assert !(n80<p6l) &&
         (n80 >= 3);
*/

}