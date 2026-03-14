int main1(){
  int i, cq, acti, jo, c;

  i=43;
  cq=0;
  acti=0;
  jo=0;
  c=(1%18)+5;

  while (c>0) {
      c--;
      cq = cq+1*1;
      jo = jo+1*1;
      acti = acti+1*1;
      cq = cq*2;
  }

  while (jo>=1) {
      jo -= 1;
      c = c+1*1;
      i = i+1*1;
      cq = cq+1*1;
      cq = cq + acti;
  }

}
