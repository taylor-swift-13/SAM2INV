int main1(int z){
  int mr, h, l2d, eg;

  mr=0;
  h=0;
  l2d=0;
  eg=(z%18)+5;

  while (eg>0) {
      l2d = l2d+z*z;
      mr = mr+z*z;
      eg--;
      h = h+z*z;
      z = z + mr;
  }

}
