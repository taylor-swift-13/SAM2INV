int main1(){
  int yuf, y, f;

  yuf=1;
  y=(1%20)+10;
  f=(1%15)+8;

  for (; y>0&&f>0; yuf++) {
      if (!(!(yuf%2==0))) {
          y -= 1;
      }
      else {
          f--;
      }
  }

}
