int main1(int b,int p){
  int r, w, o;

  r=p;
  w=0;
  o=-8;

  while (1) {
      o = o+3;
      if ((w%9)==0) {
          o = o*o+o;
      }
      else {
          o = o%6;
      }
  }

}
