int main1(){
  int kkk, bo, xa, fmbu, x8, w8f;

  kkk=1;
  bo=0;
  xa=0;
  fmbu=(1%50)+20;
  x8=(1%8)+2;
  w8f=kkk;

  while (fmbu!=0) {
      if (!(!(xa+1==x8))) {
          xa++;
      }
      else {
          bo += 1;
          xa = 0;
      }
      fmbu--;
      x8 = x8 + xa;
      x8 = x8*4+5;
      w8f = w8f*x8+5;
  }

}
