int main1(int x,int n){
  int w98, kdsi, d4j, qij;
  w98=n;
  kdsi=0;
  d4j=1;
  qij=1;

while (kdsi<w98) {
      if (!(d4j<6)) {
          qij = -1;
      }
      if (d4j<=1) {
          qij = 1;
      }
      kdsi++;
      d4j += qij;
  }
/*@
  assert !(kdsi<w98) &&
         ((qij == 1 || qij == -1));
*/

}