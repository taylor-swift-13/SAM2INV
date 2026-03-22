int main1(){
  int h, b2, kt, v;

  h=1+18;
  b2=0;
  kt=4;
  v=-6;

  while (1) {
      if (!(b2+1<=h)) {
          break;
      }
      if (!(!(b2<h/2))) {
          kt++;
      }
      else {
          kt += v;
      }
      h = (b2+1)-1;
  }

}
