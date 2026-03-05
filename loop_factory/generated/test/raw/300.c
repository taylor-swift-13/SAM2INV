int main1(){
  int l, j, fy, o;

  l=54;
  j=1;
  fy=4;
  o=0;

  while (j<l) {
      o = j%5;
      if (j>=fy) {
          fy = (j-fy)%5;
          fy = fy+o-fy;
      }
      else {
          fy = fy + o;
      }
      j++;
      fy++;
  }

}
