int main1(int p,int f){
  int ag, e, wo, cqu, yl;

  ag=f*4;
  e=0;
  wo=0;
  cqu=0;
  yl=5;

  while (wo<ag&&yl>0) {
      cqu = cqu + yl;
      wo += 1;
      p = p+ag-e;
      yl -= 1;
  }

}
