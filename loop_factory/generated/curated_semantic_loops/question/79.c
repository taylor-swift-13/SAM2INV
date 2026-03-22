int main1(int a,int b){
  int i, k, l;

  i=(a%27)+13;
  k=0;
  l=-2;


while (k+1<=i) {
      l = l+4;
      l = l%4;
  }
/*@
  assert !(k+1<=i) &&
         (i == \at(a, Pre) % 27 + 13);
*/

}
