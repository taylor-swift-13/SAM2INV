int main1(int b,int q){
  int h, r, j, w;

  h=q+19;
  r=h;
  j=0;
  w=-5;


while (j<h) {
      if (j>=h/2) {
          w = w+2;
      }
      j = j+1;
  }
/*@
  assert !(j<h) &&
         (w >= -5 && w <= -5 + 2*j && q == \at(q, Pre) && b == \at(b, Pre));
*/

}
