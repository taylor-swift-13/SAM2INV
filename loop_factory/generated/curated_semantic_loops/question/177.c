int main1(int b,int n){
  int y, e, q;

  y=9;
  e=0;
  q=n;


while (e<=y-5) {
      q = q+q;
      e = e+5;
  }
/*@
  assert !(e<=y-5) &&
         (b == \at(b, Pre));
*/

}
