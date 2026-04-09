int main1(int s){
  int p, evdq, mi, btv, w;

  p=(s%15)+17;
  evdq=p;
  mi=s;
  btv=s;
  w=s;

  while (evdq > 0) {
      evdq = (mi = mi>0 ? mi-1 : 0, btv = btv>0 ? btv-1 : 0, w = w>0 ? w-1 : 0, evdq-1);
      mi = mi + 3;
      w += mi;
  }

}
