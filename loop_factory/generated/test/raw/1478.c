int main1(){
  int sfyr, d3, w, xos;

  sfyr=1+10;
  d3=(1%18)+5;
  w=(1%15)+3;
  xos=d3;

  while (d3!=0) {
      xos += sfyr;
      d3 -= 1;
      w = w - 1;
  }

}
