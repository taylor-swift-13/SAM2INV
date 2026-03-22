int main1(){
  int vf, yw, y8, ilf, ec, r00d, wtl;

  vf=36;
  yw=0;
  y8=3;
  ilf=3;
  ec=0;
  r00d=4;
  wtl=0;

  for (; yw<vf; yw = yw + 1) {
      if (yw%3==0) {
          if (y8>0) {
              y8--;
              ec += 1;
          }
      }
      else {
          if (y8<r00d) {
              y8 = y8 + 1;
              ilf = ilf + 1;
          }
      }
      wtl++;
  }

}
