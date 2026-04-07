int main1(){
  int jyv, xb, ay;

  jyv=0;
  xb=(1%20)+10;
  ay=(1%15)+8;

  for (; xb>0&&ay>0; jyv = jyv + 1) {
      if (!(!(jyv%2==0))) {
          xb = xb - 1;
      }
      else {
          ay = ay - 1;
      }
  }

}
