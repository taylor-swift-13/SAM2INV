int main1(int a,int b){
  int e, u, t;

  e=45;
  u=0;
  t=3;


while (u<=e-1) {
      t = t+2;
      if ((u%2)==0) {
          t = t*t;
      }
      else {
          t = t*t+t;
      }
  }
/*@
  assert !(u<=e-1) &&
         (a == \at(a, Pre));
*/

}
