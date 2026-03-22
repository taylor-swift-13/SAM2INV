int main1(int h,int f){
  int r, b2, s03, fn;

  r=(f%13)+10;
  b2=1;
  s03=0;
  fn=h;

  while (b2<r) {
      s03++;
      fn += b2;
      b2 = r;
  }

}
