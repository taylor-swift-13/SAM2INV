int main1(){
  int s, y, gc, lr;

  s=(1%20)+20;
  y=s;
  gc=5;
  lr=0;

  while (lr<=s-1) {
      gc++;
      lr = lr + 1;
      gc += gc;
      if (lr<s+3) {
          gc = gc + y;
      }
      else {
          gc = gc + 3;
      }
      if ((y%5)==0) {
          gc = gc + y;
      }
  }

}
