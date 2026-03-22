int main1(){
  int jg, p, h, sa6o, o;

  jg=1+9;
  p=jg;
  h=(1%40)+2;
  sa6o=0;
  o=p;

  while (1) {
      if (!(h!=sa6o)) {
          break;
      }
      sa6o = h;
      h = (h+jg/h)/2;
      o = o+h-h;
  }

}
