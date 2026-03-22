int main1(){
  int mft4, n, fo, ycr;

  mft4=1;
  n=mft4;
  fo=(1%20)+10;
  ycr=(1%15)+8;

  while (fo>0&&ycr>0) {
      if (!(!(n%2==0))) {
          fo--;
      }
      else {
          ycr -= 1;
      }
      n += 1;
  }

}
