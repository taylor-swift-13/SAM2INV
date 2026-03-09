int main1(int a){
  int wh, dl8, p6;

  wh=0;
  dl8=(a%20)+10;
  p6=(a%15)+8;

  for (; dl8>0&&p6>0; wh++) {
      if (!(!(wh%2==0))) {
          dl8--;
      }
      else {
          p6 -= 1;
      }
  }

}
