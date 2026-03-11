int main1(int o,int u){
  int ipsj, cxn7, cd;
  ipsj=(o%20)+5;
  cxn7=(o%20)+5;
  cd=(o%20)+5;

while (ipsj>0) {
      if (cxn7>0) {
          if (cd>0) {
              ipsj--;
              cxn7--;
              cd -= 1;
          }
      }
      o += cxn7;
  }
/*@
  assert !(ipsj>0) &&
         (ipsj == cxn7);
*/

}